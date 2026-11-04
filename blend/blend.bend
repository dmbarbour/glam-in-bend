import Base

# Blend: static objects for Bend (blend/README.md; the plan,
# docs/plans/Blend_2026-11-04.md). It reads a `.blend` file into its
# structure (`blend-read`), checks its objects (`blend-objects`), binds
# the names in each concrete object's copies (`blend-resolve`) and emits
# the module (`blend-emit`); each command runs the stages up to its own
# (The command line, at the end). Run it built (blend/run.sh).
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
  NDef{+share: U32, +upd: Bool, name: List<&2, U32>, rest: List<&2, U32>, params: List<&2, List<&2, U32>>, body: List<&2, Bl>, +no: U32, +ind: U32}
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
      close.into(st, NDef{share, upd, name, rest, params, toks.lines(body), no, ind})
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
            case NDef{+share, +upd, name, rest, params, +body, +no, +dind}:
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

# Objects
# =======
#
# The module and its objects, numbered in source order, the module 0;
# each object's parents found by name, its linearization by C3 as glam
# linearizes, and the definitions each has by applying the members of its
# linearization from the last, its base, to itself (`blend-objects`).
# Errors are found per object, each reported once: where an object's
# error is its parent's already, the parent's report stands.

# a decision on a computed value: Bend matches only variables, so the arms
# are thunks, and a loop's next turn sits in an arm, inside the loop
def when(-R: Type, c: Bool, yes: Unit -> R, no: Unit -> R) -> R:
  match c:
    case True{}:
      yes(Unit{})
    case False{}:
      no(Unit{})

def on.maybe(-A: Data, -R: Type, m: Maybe<&2, A>, none: Unit -> R, some: A -> R) -> R:
  match m:
    case None{}:
      none(Unit{})
    case Some{+x}:
      some(x)

def has(xs: List<&2, U32>, +x: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+h, t}:
      U32.is_eq(h, x) || has(t, x)

def names.eq(xs: List<&2, List<&2, U32>>, ys: List<&2, List<&2, U32>>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      same(x, y) && names.eq(xt, yt)
    case _ _:
      False{}

def names.has(ns: List<&2, List<&2, U32>>, +n: List<&2, U32>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{x, t}:
      same(x, n) || names.has(t, n)

def parts.go(xs: List<&2, U32>, cur: List<&2, U32>, out: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      List.reverse(&2, List<&2, U32>, Con{List.reverse(&2, U32, cur), out})
    case Con{+h, t}:
      match h:
        case 46:
          parts.go(t, Nil{}, Con{List.reverse(&2, U32, cur), out})
        case _:
          parts.go(t, Con{h, cur}, out)

# a dotted name's parts
def parts(xs: List<&2, U32>) -> List<&2, List<&2, U32>>:
  parts.go(xs, Nil{}, Nil{})

# an object: its number, its host's, its path from the module, its
# parents as written, its members (the module's: the whole file)
type Ob is Data:
  Ob{+id: U32, +host: U32, path: List<&2, List<&2, U32>>, +abs: Bool, parents: List<&2, List<&2, U32>>, mems: List<&2, Node>, +no: U32}

# a member list being walked, with its object's number and path
type Wf is Data:
  Wf{+host: U32, path: List<&2, List<&2, U32>>, nodes: List<&2, Node>}

def count(ns: List<&2, Node>) -> Nat:
  match ns:
    case Nil{}:
      0n
    case Con{nd, t}:
      match nd:
        case NObj{+abs, name, parents, kids, +no}:
          1n+Nat.add(count(kids), count(t))
        case _:
          1n+count(t)

# the objects in source order, an object entered as it is met; fuel: a
# node or a finished member list a step
def obs.go(n: Nat, st: List<&2, Wf>, +next: U32, out: List<&2, Ob>) -> List<&2, Ob>:
  match n:
    case 0n:
      List.reverse(&2, Ob, out)
    case 1n+k:
      match st:
        case Nil{}:
          List.reverse(&2, Ob, out)
        case Con{f, rest}:
          match f:
            case Wf{+host, +path, nodes}:
              match nodes:
                case Nil{}:
                  obs.go(k, rest, next, out)
                case Con{nd, t}:
                  match nd:
                    case NObj{+abs, +name, parents, +kids, +no}:
                      obs.go(k, Con{Wf{next, List.append(&2, List<&2, U32>, path, [name]), kids}, Con{Wf{host, path, t}, rest}},
                        (next + 1 : U32), Con{Ob{next, host, List.append(&2, List<&2, U32>, path, [name]), abs, parents, kids, no}, out})
                    case _:
                      obs.go(k, Con{Wf{host, path, t}, rest}, next, out)

def obs(+tree: List<&2, Node>) -> List<&2, Ob>:
  obs.go(Nat.add(Nat.add(count(tree), count(tree)), 2n), [Wf{0, Nil{}, tree}], 1, [Ob{0, 0, Nil{}, False{}, Nil{}, tree, 0}])

def ob.or(m: Maybe<&2, Ob>) -> Ob:
  match m:
    case None{}:
      Ob{0, 0, Nil{}, False{}, Nil{}, Nil{}, 0}
    case Some{o}:
      o

def ob.at(+obs: List<&2, Ob>, +id: U32) -> Ob:
  ob.or(List.get(&2, Ob, obs, U32.to_nat(id)))

def ob.path(o: Ob) -> List<&2, List<&2, U32>>:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no}:
      path

def ob.host(o: Ob) -> U32:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no}:
      host

def ob.abs(o: Ob) -> Bool:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no}:
      abs

def ob.no(o: Ob) -> U32:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no}:
      no

def ob.mems(o: Ob) -> List<&2, Node>:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no}:
      mems

def dots(ps: List<&2, List<&2, U32>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      match t:
        case Nil{}:
          p
        case Con{h, r}:
          List.append(&2, U32, p, Con{46, dots(Con{h, r})})

def ob.name.of(+path: List<&2, List<&2, U32>>) -> String:
  match path:
    case Nil{}:
      "the module"
    case Con{h, t}:
      text(dots(Con{h, t}))

# an object's name as messages give it; the module's, "the module"
def ob.name(+obs: List<&2, Ob>, +id: U32) -> String:
  ob.name.of(ob.path(ob.at(obs, id)))

# the first object at path p
def find.path(+obs: List<&2, Ob>, +p: List<&2, List<&2, U32>>) -> Maybe<&2, U32>:
  match obs:
    case Nil{}:
      None{}
    case Con{+o, +t}:
      match o:
        case Ob{+id, +host, +path, +abs, parents, mems, +no}:
          when(Maybe<&2, U32>, names.eq(path, p), u => Some{id}, u => find.path(t, p))

# a parent's name found from scope s outward to the module: the object at
# s's path and the name's parts; fuel, the objects' count
def resolve(n: Nat, +obs: List<&2, Ob>, +s: U32, +segs: List<&2, List<&2, U32>>) -> Maybe<&2, U32>:
  match n:
    case 0n:
      None{}
    case 1n++k:
      on.maybe(U32, Maybe<&2, U32>, find.path(obs, List.append(&2, List<&2, U32>, ob.path(ob.at(obs, s)), segs)),
        u => when(Maybe<&2, U32>, U32.is_eq(s, 0), v => None{}, v => resolve(k, obs, ob.host(ob.at(obs, s)), segs)),
        x => Some{x})

def parent.find(+obs: List<&2, Ob>, +host: U32, +p: List<&2, U32>) -> Maybe<&2, U32>:
  resolve(List.length(&2, Ob, obs), obs, host, parts(p))

# an object's parents found, those named by nothing left out
def pids.go(ps: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +host: U32) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, +t}:
      on.maybe(U32, List<&2, U32>, parent.find(obs, host, p), u => pids.go(t, obs, host), x => Con{x, pids.go(t, obs, host)})

# xs, each kept where it first appears
def uniq(xs: List<&2, U32>, +seen: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, U32>, has(seen, x), u => uniq(t, seen), u => Con{x, uniq(t, Con{x, seen})})

# a parent named twice is one parent
def pids.of(o: Ob, +obs: List<&2, Ob>) -> List<&2, U32>:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no}:
      uniq(pids.go(parents, obs, host), Nil{})

# each object's parents, by number
def pids(os: List<&2, Ob>, +obs: List<&2, Ob>) -> List<&2, List<&2, U32>>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Con{pids.of(o, obs), pids(t, obs)}

# an error: its line and its message
type Er is Data:
  Er{+no: U32, msg: String}

def er.le(a: Er, b: Er) -> Bool:
  match a b:
    case Er{+x, m} Er{+y, n}:
      U32.is_le(x, y)

def er.parents(ps: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +id: U32, +host: U32, +no: U32) -> List<&2, Er>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, +t}:
      on.maybe(U32, List<&2, Er>, parent.find(obs, host, p),
        u => Con{Er{no, ob.name(obs, id) ++ " extends " ++ text(p) ++ ", which names no object"}, er.parents(t, obs, id, host, no)},
        x => er.parents(t, obs, id, host, no))

def er.twice(+obs: List<&2, Ob>, +id: U32, +path: List<&2, List<&2, U32>>, +no: U32) -> List<&2, Er>:
  on.maybe(U32, List<&2, Er>, find.path(obs, path), u => Nil{},
    +x => when(List<&2, Er>, U32.is_eq(x, id), v => Nil{},
      v => [Er{no, "object " ++ ob.name(obs, id) ++ " is defined at line " ++ U32.show(ob.no(ob.at(obs, x))) ++ " already"}]))

# a member list's lines Blend cannot read, and imports inside an object
def er.mems(ns: List<&2, Node>, +top: Bool) -> List<&2, Er>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, +t}:
      match nd:
        case NBad{txt, +no}:
          Con{Er{no, "Blend cannot read this line: " ++ text(txt)}, er.mems(t, top)}
        case NImport{txt, +no}:
          when(List<&2, Er>, top, u => er.mems(t, top),
            u => Con{Er{no, "an import belongs to the module, outside every object"}, er.mems(t, top)})
        case _:
          er.mems(t, top)

# each object's errors of reading and naming
def er.obs(os: List<&2, Ob>, +obs: List<&2, Ob>) -> List<&2, Er>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      match o:
        case Ob{+id, +host, +path, +abs, +parents, mems, +no}:
          List.append(&2, Er, er.mems(mems, U32.is_eq(id, 0)),
            List.append(&2, Er, when(List<&2, Er>, U32.is_eq(id, 0), u => Nil{}, u => er.twice(obs, id, path, no)),
              List.append(&2, Er, er.parents(parents, obs, id, host, no), er.obs(t, obs))))

# C3
# --
#
# An object's linearization is itself, then the merge of its parents'
# linearizations and its parents' list: each turn takes the first head
# that is in no list's tail. The lists keep their owners, for the message
# when no head is free.

type Sq is Data:
  Sq{+owner: U32, xs: List<&2, U32>}

def in_tails(ss: List<&2, Sq>, +h: U32) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case Con{s, t}:
      match s:
        case Sq{+o, xs}:
          match xs:
            case Nil{}:
              in_tails(t, h)
            case Con{x, r}:
              has(r, h) || in_tails(t, h)

# the first head in no tail
def c3.good(cs: List<&2, Sq>, +all: List<&2, Sq>) -> Maybe<&2, U32>:
  match cs:
    case Nil{}:
      None{}
    case Con{c, t}:
      match c:
        case Sq{+o, xs}:
          match xs:
            case Nil{}:
              c3.good(t, all)
            case Con{+h, r}:
              when(Maybe<&2, U32>, in_tails(all, h), u => c3.good(t, all), u => Some{h})

def c3.head.drop(xs: List<&2, U32>, +h: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, U32>, U32.is_eq(x, h), u => t, u => Con{x, t})

def c3.keep(+o: U32, xs: List<&2, U32>, rest: List<&2, Sq>) -> List<&2, Sq>:
  match xs:
    case Nil{}:
      rest
    case Con{x, r}:
      Con{Sq{o, Con{x, r}}, rest}

# the lists, h taken from their heads, the empty ones dropped
def c3.take(ss: List<&2, Sq>, +h: U32) -> List<&2, Sq>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      match s:
        case Sq{+o, xs}:
          c3.keep(o, c3.head.drop(xs, h), c3.take(t, h))

type Mg is Data:
  MOk{ord: List<&2, U32>}
  MFail{seqs: List<&2, Sq>}

# fuel: the lists' lengths, a head taken each turn
def c3.merge(n: Nat, +seqs: List<&2, Sq>, +out: List<&2, U32>) -> Mg:
  match n:
    case 0n:
      MFail{seqs}
    case 1n++k:
      match seqs:
        case Nil{}:
          MOk{List.reverse(&2, U32, out)}
        case Con{+s, +t}:
          on.maybe(U32, Mg, c3.good(Con{s, t}, Con{s, t}), u => MFail{Con{s, t}},
            +h => c3.merge(k, c3.take(Con{s, t}, h), Con{h, out}))

def sqs.len(ss: List<&2, Sq>) -> Nat:
  match ss:
    case Nil{}:
      0n
    case Con{s, t}:
      match s:
        case Sq{+o, xs}:
          Nat.add(List.length(&2, U32, xs), sqs.len(t))

# a linearization found: whether it is sound (its parents' too), and its order
type Lz is Data:
  Lz{+ok: Bool, ord: List<&2, U32>}

def lz.or(m: Maybe<&2, Maybe<&2, Lz>>) -> Maybe<&2, Lz>:
  match m:
    case None{}:
      None{}
    case Some{z}:
      z

def lz.at(+lins: List<&2, Maybe<&2, Lz>>, +id: U32) -> Maybe<&2, Lz>:
  lz.or(List.get(&2, Maybe<&2, Lz>, lins, U32.to_nat(id)))

def lin.seqs.k(+ok: Bool, +p: U32, ord: List<&2, U32>, rest: Maybe<&2, Maybe<&2, List<&2, Sq>>>) -> Maybe<&2, Maybe<&2, List<&2, Sq>>>:
  match ok:
    case True{}:
      match rest:
        case None{}:
          None{}
        case Some{r}:
          match r:
            case Some{ss}:
              Some{Some{Con{Sq{p, ord}, ss}}}
            case None{}:
              Some{None{}}
    case False{}:
      match rest:
        case None{}:
          None{}
        case Some{r}:
          Some{None{}}

def lin.seqs.z(+p: U32, m: Maybe<&2, Lz>, rest: Maybe<&2, Maybe<&2, List<&2, Sq>>>) -> Maybe<&2, Maybe<&2, List<&2, Sq>>>:
  match m:
    case None{}:
      None{}
    case Some{z}:
      match z:
        case Lz{+ok, ord}:
          lin.seqs.k(ok, p, ord, rest)

# the parents' linearizations as lists to merge, None while one is missing
# (an unsound one: Some of None, its error its own)
def lin.seqs(ps: List<&2, U32>, +lins: List<&2, Maybe<&2, Lz>>) -> Maybe<&2, Maybe<&2, List<&2, Sq>>>:
  match ps:
    case Nil{}:
      Some{Some{Nil{}}}
    case Con{+p, t}:
      lin.seqs.z(p, lz.at(lins, p), lin.seqs(t, lins))

def lin.mg(+id: U32, m: Mg) -> Lz:
  match m:
    case MOk{ord}:
      Lz{True{}, Con{id, ord}}
    case MFail{ss}:
      Lz{False{}, [id]}

def lin.of(+id: U32, +ps: List<&2, U32>, ss: Maybe<&2, List<&2, Sq>>) -> Lz:
  match ss:
    case None{}:
      Lz{False{}, [id]}
    case Some{+seqs}:
      lin.mg(id, c3.merge(1n+sqs.len(List.append(&2, Sq, seqs, [Sq{id, ps}])), c3.take(List.append(&2, Sq, seqs, [Sq{id, ps}]), 4294967295), Nil{}))

def lin.try(+id: U32, +ps: List<&2, U32>, m: Maybe<&2, Maybe<&2, List<&2, Sq>>>) -> Maybe<&2, Lz>:
  match m:
    case None{}:
      None{}
    case Some{ss}:
      Some{lin.of(id, ps, ss)}

# a round: each object not yet linearized whose parents are
def lin.round(ps: List<&2, List<&2, U32>>, cur: List<&2, Maybe<&2, Lz>>, +id: U32, +all: List<&2, Maybe<&2, Lz>>) -> List<&2, Maybe<&2, Lz>>:
  match ps cur:
    case Con{+p, pt} Con{c, ct}:
      match c:
        case Some{z}:
          Con{Some{z}, lin.round(pt, ct, (id + 1 : U32), all)}
        case None{}:
          Con{lin.try(id, p, lin.seqs(p, all)), lin.round(pt, ct, (id + 1 : U32), all)}
    case _ _:
      Nil{}

def lin.go(n: Nat, +pss: List<&2, List<&2, U32>>, +lins: List<&2, Maybe<&2, Lz>>) -> List<&2, Maybe<&2, Lz>>:
  match n:
    case 0n:
      lins
    case 1n+k:
      lin.go(k, pss, lin.round(pss, lins, 0, lins))

def nones(ps: List<&2, List<&2, U32>>) -> List<&2, Maybe<&2, Lz>>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{None{}, nones(t)}

# every object's linearization, None where its parents lead back to it;
# a round for each object at most, as each round linearizes one at least
def lins(+pss: List<&2, List<&2, U32>>) -> List<&2, Maybe<&2, Lz>>:
  lin.go(1n+List.length(&2, List<&2, U32>, pss), pss, nones(pss))

# two lists that order two heads both ways, for the message
type Cf is Data:
  Cf{+a: U32, +x: U32, +b: U32, +y: U32}

def cf.with(ss: List<&2, Sq>, +a: U32, +x: U32, +r: List<&2, U32>) -> Maybe<&2, Cf>:
  match ss:
    case Nil{}:
      None{}
    case Con{s, t}:
      match s:
        case Sq{+b, xs}:
          match xs:
            case Nil{}:
              cf.with(t, a, x, r)
            case Con{+y, +r2}:
              when(Maybe<&2, Cf>, has(r2, x) && has(r, y), u => Some{Cf{a, x, b, y}}, u => cf.with(t, a, x, r))

def cf.find(cs: List<&2, Sq>, +all: List<&2, Sq>) -> Maybe<&2, Cf>:
  match cs:
    case Nil{}:
      None{}
    case Con{c, t}:
      match c:
        case Sq{+a, xs}:
          match xs:
            case Nil{}:
              cf.find(t, all)
            case Con{+x, +r}:
              on.maybe(Cf, Maybe<&2, Cf>, cf.with(all, a, x, r), u => cf.find(t, all), f => Some{f})

def cf.msg(+obs: List<&2, Ob>, m: Maybe<&2, Cf>) -> String:
  match m:
    case None{}:
      "no order fits its parents' orders"
    case Some{f}:
      match f:
        case Cf{+a, +x, +b, +y}:
          ob.name(obs, a) ++ " puts " ++ ob.name(obs, x) ++ " before " ++ ob.name(obs, y) ++ ", and " ++
            ob.name(obs, b) ++ " puts " ++ ob.name(obs, y) ++ " before " ++ ob.name(obs, x)

def c3.why(+obs: List<&2, Ob>, +id: U32, m: Mg) -> List<&2, Er>:
  match m:
    case MOk{ord}:
      Nil{}
    case MFail{+ss}:
      [Er{ob.no(ob.at(obs, id)), ob.name(obs, id) ++ " has no C3 linearization: " ++ cf.msg(obs, cf.find(ss, ss))}]

def c3.er(+obs: List<&2, Ob>, +id: U32, +ps: List<&2, U32>, ss: Maybe<&2, List<&2, Sq>>) -> List<&2, Er>:
  match ss:
    case None{}:
      Nil{}
    case Some{+seqs}:
      c3.why(obs, id, c3.merge(1n+sqs.len(List.append(&2, Sq, seqs, [Sq{id, ps}])), c3.take(List.append(&2, Sq, seqs, [Sq{id, ps}]), 4294967295), Nil{}))

def c3.er.k(+obs: List<&2, Ob>, +id: U32, +ps: List<&2, U32>, m: Maybe<&2, Maybe<&2, List<&2, Sq>>>) -> List<&2, Er>:
  match m:
    case None{}:
      Nil{}
    case Some{ss}:
      c3.er(obs, id, ps, ss)

# the linearization errors: an object its parents lead back to, and one
# whose sound parents have no merge
def er.lins(ps: List<&2, List<&2, U32>>, ls: List<&2, Maybe<&2, Lz>>, +id: U32, +obs: List<&2, Ob>, +all: List<&2, Maybe<&2, Lz>>) -> List<&2, Er>:
  match ps ls:
    case Con{+p, +pt} Con{l, +lt}:
      match l:
        case None{}:
          Con{Er{ob.no(ob.at(obs, id)), ob.name(obs, id) ++ " inherits from itself"}, er.lins(pt, lt, (id + 1 : U32), obs, all)}
        case Some{z}:
          match z:
            case Lz{+ok, ord}:
              when(List<&2, Er>, ok, u => er.lins(pt, lt, (id + 1 : U32), obs, all),
                u => List.append(&2, Er, c3.er.k(obs, id, p, lin.seqs(p, all)), er.lins(pt, lt, (id + 1 : U32), obs, all)))
    case _ _:
      Nil{}

# Definitions
# -----------
#
# An object's definitions: its linearization's members applied from its
# base to itself, each name with the objects that gave it, the latest
# first (an upd's prior is the next), and the line of the latest.

type En is Data:
  En{name: List<&2, U32>, chain: List<&2, U32>, +no: U32}

# a member's error: its object and line, its kind (0 an introduction of a
# name another object has, 1 a name its object gives twice, 2 an update of
# nothing), its name and upd or def, and the object and line it met
type Fe is Data:
  Fe{+q: U32, +mno: U32, +kind: U32, name: List<&2, U32>, +upd: Bool, +origin: U32, +ono: U32}

type Fd is Data:
  Fd{map: List<&2, En>, fes: List<&2, Fe>}

def en.find(es: List<&2, En>, +n: List<&2, U32>) -> Maybe<&2, En>:
  match es:
    case Nil{}:
      None{}
    case Con{+e, t}:
      match e:
        case En{+name, chain, +no}:
          when(Maybe<&2, En>, same(name, n), u => Some{e}, u => en.find(t, n))

def en.set(es: List<&2, En>, +e: En, +n: List<&2, U32>) -> List<&2, En>:
  match es:
    case Nil{}:
      [e]
    case Con{+x, +t}:
      match x:
        case En{+name, chain, +no}:
          when(List<&2, En>, same(name, n), u => Con{e, t}, u => Con{x, en.set(t, e, n)})

def en.head(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{+h, t}:
      h

# an introduction met an entry: twice in one object, or from another
def fd.def.at(+q: U32, +no: U32, +name: List<&2, U32>, e: En, map: List<&2, En>, fes: List<&2, Fe>) -> Fd:
  match e:
    case En{n, +chain, +eno}:
      Fd{en.set(map, En{name, [q], no}, name),
        Con{Fe{q, no, when(U32, U32.is_eq(en.head(chain), q), u => 1, u => 0), name, False{}, en.head(chain), eno}, fes}}

def fd.upd.at(+q: U32, +no: U32, +name: List<&2, U32>, e: En, +map: List<&2, En>, +fes: List<&2, Fe>) -> Fd:
  match e:
    case En{n, +chain, +eno}:
      when(Fd, U32.is_eq(en.head(chain), q),
        u => Fd{en.set(map, En{name, chain, no}, name), Con{Fe{q, no, 1, name, True{}, q, eno}, fes}},
        u => Fd{en.set(map, En{name, Con{q, chain}, no}, name), fes})

def fd.def(+q: U32, +upd: Bool, +name: List<&2, U32>, +no: U32, d: Fd) -> Fd:
  match d:
    case Fd{+map, +fes}:
      on.maybe(En, Fd, en.find(map, name),
        u => when(Fd, upd,
          v => Fd{en.set(map, En{name, [q], no}, name), Con{Fe{q, no, 2, name, True{}, q, no}, fes}},
          v => Fd{en.set(map, En{name, [q], no}, name), fes}),
        +e => when(Fd, upd, v => fd.upd.at(q, no, name, e, map, fes), v => fd.def.at(q, no, name, e, map, fes)))

def fd.mems(ns: List<&2, Node>, +q: U32, d: Fd) -> Fd:
  match ns:
    case Nil{}:
      d
    case Con{nd, t}:
      match nd:
        case NDef{+share, +upd, name, rest, params, body, +no, +ind}:
          fd.mems(t, q, fd.def(q, upd, name, no, d))
        case _:
          fd.mems(t, q, d)

def fd.obs(qs: List<&2, U32>, +obs: List<&2, Ob>, d: Fd) -> Fd:
  match qs:
    case Nil{}:
      d
    case Con{+q, t}:
      fd.obs(t, obs, fd.mems(ob.mems(ob.at(obs, q)), q, d))

# an object's definitions and its members' errors, its linearization sound
def fold(+obs: List<&2, Ob>, l: Maybe<&2, Lz>) -> Maybe<&2, Fd>:
  match l:
    case None{}:
      None{}
    case Some{z}:
      match z:
        case Lz{+ok, ord}:
          when(Maybe<&2, Fd>, ok, u => Some{fd.obs(List.reverse(&2, U32, ord), obs, Fd{Nil{}, Nil{}})}, u => None{})

def folds(ls: List<&2, Maybe<&2, Lz>>, +obs: List<&2, Ob>) -> List<&2, Maybe<&2, Fd>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      Con{fold(obs, l), folds(t, obs)}

def fd.or(m: Maybe<&2, Maybe<&2, Fd>>) -> Maybe<&2, Fd>:
  match m:
    case None{}:
      None{}
    case Some{f}:
      f

def fd.at(+fds: List<&2, Maybe<&2, Fd>>, +id: U32) -> Maybe<&2, Fd>:
  fd.or(List.get(&2, Maybe<&2, Fd>, fds, U32.to_nat(id)))

def fe.lines(fes: List<&2, Fe>) -> List<&2, U32>:
  match fes:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      match f:
        case Fe{+q, +mno, +kind, name, +upd, +origin, +ono}:
          Con{mno, fe.lines(t)}

def fd.lines(m: Maybe<&2, Fd>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{d}:
      match d:
        case Fd{map, fes}:
          fe.lines(fes)

# the members' error lines of an object's parents: their own reports
def seen(ps: List<&2, U32>, +fds: List<&2, Maybe<&2, Fd>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      List.append(&2, U32, fd.lines(fd.at(fds, p)), seen(t, fds))

def kw(+upd: Bool) -> String:
  match upd:
    case True{}:
      "upd "
    case False{}:
      "def "

def fe.msg(+obs: List<&2, Ob>, +id: U32, f: Fe) -> Er:
  match f:
    case Fe{+q, +mno, +kind, +name, +upd, +origin, +ono}:
      match kind:
        case 1:
          Er{mno, text(name) ++ " is given twice in " ++ ob.name(obs, q) ++ ", at lines " ++ U32.show(ono) ++ " and " ++ U32.show(mno)}
        case 2:
          Er{mno, kw(upd) ++ text(name) ++ ": " ++ ob.name(obs, q) ++ " has no " ++ text(name) ++ " to update (introduce it with def)"}
        case _:
          when(Er, U32.is_eq(q, id),
            u => Er{mno, kw(upd) ++ text(name) ++ ": " ++ ob.name(obs, q) ++ " has " ++ text(name) ++ " already, from " ++
              ob.name(obs, origin) ++ " (update it with upd)"},
            u => Er{ob.no(ob.at(obs, id)), ob.name(obs, id) ++ " has " ++ text(name) ++ " from both " ++ ob.name(obs, origin) ++
              " and " ++ ob.name(obs, q) ++ ", each introducing it with def"})

def er.fes(fes: List<&2, Fe>, +skip: List<&2, U32>, +obs: List<&2, Ob>, +id: U32) -> List<&2, Er>:
  match fes:
    case Nil{}:
      Nil{}
    case Con{+f, +t}:
      match f:
        case Fe{+q, +mno, +kind, +name, +upd, +origin, +ono}:
          when(List<&2, Er>, has(skip, mno), u => er.fes(t, skip, obs, id),
            u => Con{fe.msg(obs, id, Fe{q, mno, kind, name, upd, origin, ono}), er.fes(t, skip, obs, id)})

# Declarations
# ------------

# a declared name, the object declaring it, and the line
type Dn is Data:
  Dn{name: List<&2, U32>, +q: U32, +no: U32}

def decl.tag(ns: List<&2, List<&2, U32>>, +q: U32, +no: U32) -> List<&2, Dn>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{Dn{n, q, no}, decl.tag(t, q, no)}

def decl.names(ns: List<&2, Node>, +q: U32) -> List<&2, Dn>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, t}:
      match nd:
        case NDecl{names, +no}:
          List.append(&2, Dn, decl.tag(names, q, no), decl.names(t, q))
        case _:
          decl.names(t, q)

def decl.obs(qs: List<&2, U32>, +obs: List<&2, Ob>) -> List<&2, Dn>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{+q, t}:
      List.append(&2, Dn, decl.names(ob.mems(ob.at(obs, q)), q), decl.obs(t, obs))

def decl.missing(+obs: List<&2, Ob>, +id: U32, +n: List<&2, U32>, +q: U32, +no: U32) -> Er:
  when(Er, U32.is_eq(id, 0),
    u => Er{no, "the module declares " ++ text(n) ++ " and defines none"},
    u => Er{ob.no(ob.at(obs, id)), ob.name(obs, id) ++ " defines no " ++ text(n) ++ ", which " ++ ob.name(obs, q) ++
      " declares (or mark " ++ ob.name(obs, id) ++ " abstract)"})

def decl.check.k(+obs: List<&2, Ob>, +id: U32, +map: List<&2, En>, +done: List<&2, List<&2, U32>>, +n: List<&2, U32>, +q: U32, +no: U32) -> List<&2, Er>:
  when(List<&2, Er>, names.has(done, n) || Maybe.is_some(&2, En, en.find(map, n)), u => Nil{},
    u => [decl.missing(obs, id, n, q, no)])

def decl.check(+obs: List<&2, Ob>, +id: U32, +map: List<&2, En>, +done: List<&2, List<&2, U32>>, d: Dn) -> List<&2, Er>:
  match d:
    case Dn{+n, +q, +no}:
      decl.check.k(obs, id, map, done, n, q, no)

def decl.pair.name(d: Dn) -> List<&2, U32>:
  match d:
    case Dn{n, +q, +no}:
      n

def decl.go(ds: List<&2, Dn>, +obs: List<&2, Ob>, +id: U32, +map: List<&2, En>, +done: List<&2, List<&2, U32>>) -> List<&2, Er>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{+d, t}:
      List.append(&2, Er, decl.check(obs, id, map, done, d), decl.go(t, obs, id, map, Con{decl.pair.name(d), done}))

# a concrete object's declared names it gives no definition, each once
def er.decls(+obs: List<&2, Ob>, +id: U32, +ord: List<&2, U32>, +map: List<&2, En>) -> List<&2, Er>:
  when(List<&2, Er>, ob.abs(ob.at(obs, id)), u => Nil{}, u => decl.go(decl.obs(List.reverse(&2, U32, ord), obs), obs, id, map, Nil{}))

def er.def.k(+obs: List<&2, Ob>, +id: U32, +ps: List<&2, U32>, +fds: List<&2, Maybe<&2, Fd>>, +ord: List<&2, U32>, m: Maybe<&2, Fd>) -> List<&2, Er>:
  match m:
    case None{}:
      Nil{}
    case Some{d}:
      match d:
        case Fd{+map, fes}:
          List.append(&2, Er, er.fes(fes, seen(ps, fds), obs, id), er.decls(obs, id, ord, map))

def lz.ord(m: Maybe<&2, Lz>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{z}:
      match z:
        case Lz{+ok, ord}:
          ord

# each object's errors of definition and declaration
def er.defs(ps: List<&2, List<&2, U32>>, fs: List<&2, Maybe<&2, Fd>>, ls: List<&2, Maybe<&2, Lz>>, +id: U32, +obs: List<&2, Ob>, +fds: List<&2, Maybe<&2, Fd>>) -> List<&2, Er>:
  match ps fs ls:
    case Con{+p, pt} Con{f, ft} Con{l, lt}:
      List.append(&2, Er, er.def.k(obs, id, p, fds, lz.ord(l), f), er.defs(pt, ft, lt, (id + 1 : U32), obs, fds))
    case _ _ _:
      Nil{}

# The objects, printed
# --------------------

def show.ids(+obs: List<&2, Ob>, xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, t}:
      match t:
        case Nil{}:
          ob.name(obs, x)
        case Con{h, r}:
          ob.name(obs, x) ++ ", " ++ show.ids(obs, Con{h, r})

def show.chain(+obs: List<&2, Ob>, xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, t}:
      match t:
        case Nil{}:
          ob.name(obs, x)
        case Con{h, r}:
          ob.name(obs, x) ++ " < " ++ show.chain(obs, Con{h, r})

def show.ens(+obs: List<&2, Ob>, es: List<&2, En>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, t}:
      match e:
        case En{name, chain, +no}:
          "  " ++ text(name) ++ ": " ++ show.chain(obs, chain) ++ "\n" ++ show.ens(obs, t)

def show.fd(+obs: List<&2, Ob>, m: Maybe<&2, Fd>) -> String:
  match m:
    case None{}:
      ""
    case Some{d}:
      match d:
        case Fd{map, fes}:
          show.ens(obs, map)

def show.abs.of(+a: Bool) -> String:
  match a:
    case True{}:
      "abstract "
    case False{}:
      ""

def show.ob(+obs: List<&2, Ob>, o: Ob, l: Maybe<&2, Lz>, f: Maybe<&2, Fd>) -> String:
  match o:
    case Ob{+id, +host, path, +abs, parents, mems, +no}:
      when(String, U32.is_eq(id, 0), u => "the module",
        u => show.abs.of(abs) ++ ob.name(obs, id) ++ ": " ++ show.ids(obs, lz.ord(l))) ++ "\n" ++ show.fd(obs, f)

# each object, its linearization, and each definition it has with the
# objects that gave it, the final first
def show.obs(os: List<&2, Ob>, ls: List<&2, Maybe<&2, Lz>>, fs: List<&2, Maybe<&2, Fd>>, +obs: List<&2, Ob>) -> String:
  match os ls fs:
    case Con{o, ot} Con{l, lt} Con{f, ft}:
      show.ob(obs, o, l, f) ++ show.obs(ot, lt, ft, obs)
    case _ _ _:
      ""

def show.ers.more(es: List<&2, Er>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, t}:
      "\n"

def er.at(+no: U32) -> String:
  match no:
    case 0:
      ""
    case _:
      ":" ++ U32.show(no)

# errors, each `FILE:LINE: message`, a line 0 left out
def show.ers(+file: String, es: List<&2, Er>) -> String:
  match es:
    case Nil{}:
      ""
    case Con{e, +t}:
      match e:
        case Er{+no, msg}:
          file ++ er.at(no) ++ ": " ++ msg ++ show.ers.more(t) ++ show.ers(file, t)

# References
# ==========
#
# Each concrete object's definitions, its own copies, their bodies'
# names bound (`blend-resolve`): a bare name to the final definition of
# the innermost object that has it, the concrete object itself first,
# then the hosts of the object that wrote the body; a dotted name to an
# object's definition (`Outer.Inner.path`), the longest object path
# first; `_name` to the definition the writer's replaced, `^name` to its
# host's, `~name` as a bare name, the mark kept. A body's locals are its
# parameters and binders; a local named as a definition is an error
# (`shadowing-is-an-error`), so any other name a definition has is a
# reference. The rest is Bend's.

# the module, its objects, their linearizations and definitions
type Cx is Data:
  Cx{obs: List<&2, Ob>, ls: List<&2, Maybe<&2, Lz>>, fs: List<&2, Maybe<&2, Fd>>}

def cx.obs(c: Cx) -> List<&2, Ob>:
  match c:
    case Cx{obs, ls, fs}:
      obs

def fd.map(m: Maybe<&2, Fd>) -> List<&2, En>:
  match m:
    case None{}:
      Nil{}
    case Some{d}:
      match d:
        case Fd{map, fes}:
          map

def cx.map(c: Cx, +id: U32) -> List<&2, En>:
  match c:
    case Cx{obs, ls, fs}:
      fd.map(fd.at(fs, id))

def cx.ord(c: Cx, +id: U32) -> List<&2, U32>:
  match c:
    case Cx{obs, ls, fs}:
      lz.ord(lz.at(ls, id))

def has.def(+map: List<&2, En>, +n: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, En, en.find(map, n))

# an object's hosts, innermost first, the module last; the module's none
def hosts.go(n: Nat, +obs: List<&2, Ob>, +id: U32) -> List<&2, U32>:
  match n:
    case 0n:
      Nil{}
    case 1n++k:
      when(List<&2, U32>, U32.is_eq(id, 0), u => Nil{},
        u => Con{ob.host(ob.at(obs, id)), hosts.go(k, obs, ob.host(ob.at(obs, id)))})

def hosts(+obs: List<&2, Ob>, +id: U32) -> List<&2, U32>:
  hosts.go(1n+List.length(&2, Ob, obs), obs, id)

# A body's locals
# ---------------

def tok.sym(t: Tok, +c: U32) -> Bool:
  match t:
    case TSym{+x}:
      U32.is_eq(x, c)
    case _:
      False{}

# whether ts begins with the symbol c
def tok.sym.head(ts: List<&2, Tok>, +c: U32) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, r}:
      tok.sym(t, c)

def tok.solid(ts: List<&2, Tok>) -> List<&2, Tok>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      match t:
        case TSp{x}:
          tok.solid(r)
        case TCom{x}:
          tok.solid(r)
        case _:
          Con{t, tok.solid(r)}

def tok.brace(ts: List<&2, Tok>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, r}:
      tok.sym(t, 123)

def tok.arrow(ts: List<&2, Tok>) -> Bool:
  match ts:
    case Con{a, r}:
      match r:
        case Con{b, r2}:
          tok.sym(a, 61) && tok.sym(b, 62)
        case Nil{}:
          False{}
    case Nil{}:
      False{}

def is.wild(+x: List<&2, U32>) -> Bool:
  same(x, codes("_"))

# a pattern's binders: its names, but constructors (a name before `{`)
# and `_`; up to the pattern's `:`
def pat.names(+ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, +r}:
      match t:
        case TName{+x}:
          when(List<&2, List<&2, U32>>, tok.brace(r) || is.wild(x), u => pat.names(r), u => Con{x, pat.names(r)})
        case TSym{+c}:
          match c:
            case 58:
              Nil{}
            case _:
              pat.names(r)
        case _:
          pat.names(r)

# a let's binders: names, brackets, commas and marks, then a lone `=`
def let.names(+ts: List<&2, Tok>, +acc: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, +r}:
      match t:
        case TName{+x}:
          let.names(r, when(List<&2, List<&2, U32>>, tok.brace(r) || is.wild(x), u => acc, u => Con{x, acc}))
        case TSym{+c}:
          match c:
            case 61:
              when(List<&2, List<&2, U32>>, tok.arrow(Con{TSym{c}, r}) || tok.sym.head(r, 61), u => Nil{}, u => acc)
            case 40:
              let.names(r, acc)
            case 41:
              let.names(r, acc)
            case 44:
              let.names(r, acc)
            case 43:
              let.names(r, acc)
            case 45:
              let.names(r, acc)
            case 123:
              let.names(r, acc)
            case 125:
              let.names(r, acc)
            case _:
              Nil{}
        case _:
          Nil{}

# a lambda's binders: each name before `=>`
def lam.names(+ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, +r}:
      match t:
        case TName{+x}:
          when(List<&2, List<&2, U32>>, tok.arrow(r), u => Con{x, lam.names(r)}, u => lam.names(r))
        case _:
          lam.names(r)

# a bind's or an annotated let's binder: a line's first name before `:`
def bind.name(+ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, +r}:
      match t:
        case TSym{+c}:
          match c:
            case 43:
              bind.name(r)
            case 45:
              bind.name(r)
            case _:
              Nil{}
        case TName{+x}:
          when(List<&2, List<&2, U32>>, tok.sym.head(r, 58), u => [x], u => Nil{})
        case _:
          Nil{}

def is.case(ts: List<&2, Tok>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case Con{t, r}:
      match t:
        case TName{x}:
          same(x, codes("case"))
        case _:
          False{}

def line.names.k(+pat: Bool, +ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  match pat:
    case True{}:
      List.append(&2, List<&2, U32>, pat.names(List.tail(&2, Tok, ts)), lam.names(ts))
    case False{}:
      List.append(&2, List<&2, U32>, let.names(ts, Nil{}), List.append(&2, List<&2, U32>, bind.name(ts), lam.names(ts)))

def line.names(+ts: List<&2, Tok>) -> List<&2, List<&2, U32>>:
  line.names.k(is.case(tok.solid(ts)), tok.solid(ts))

# A name bound
# ------------

# where a name points: a final definition (obj's), or a prior (the one
# origin gave, in obj's copy)
type Rf is Data:
  Rf{+obj: U32, name: List<&2, U32>, +prior: Bool, +origin: U32}

# a body's token, a reference resolved or as written
type Rt is Data:
  RT{t: Tok}
  RR{+mark: U32, ref: Rf}

type Rl is Data:
  Rl{+no: U32, +ind: U32, ts: List<&2, Rt>}

# a definition in a concrete object's copy: its name, the object whose
# member it is, whether it is a prior
type In is Data:
  In{name: List<&2, U32>, +q: U32, +prior: Bool}

# a token resolved, the errors it raised, the priors it reached
type Rr is Data:
  Rr{rt: Rt, ers: List<&2, Er>, ins: List<&2, In>}

# a name token's text
def tok.txt(t: Tok) -> List<&2, U32>:
  match t:
    case TName{x}:
      x
    case _:
      Nil{}

def rr.tok(t: Tok) -> Rr:
  Rr{RT{t}, Nil{}, Nil{}}

def rr.er(t: Tok, +no: U32, msg: String) -> Rr:
  Rr{RT{t}, [Er{no, msg}], Nil{}}

def carets(xs: List<&2, U32>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{+h, t}:
      match h:
        case 94:
          1n+carets(t)
        case _:
          0n

def nth(+xs: List<&2, U32>, n: Nat) -> Maybe<&2, U32>:
  List.get(&2, U32, xs, n)

# a reference to obj's final n, an error where obj is abstract
def rr.final(+cx: Cx, +obj: U32, +mark: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  when(Rr, ob.abs(ob.at(cx.obs(cx), obj)),
    u => rr.er(t, no, text(tok.txt(t)) ++ " names a definition of " ++ ob.name(cx.obs(cx), obj) ++ ", which is abstract and emits nothing"),
    u => Rr{RR{mark, Rf{obj, n, False{}, obj}}, Nil{}, Nil{}})

# a bare name: the concrete object's, then each host's, innermost first
def look(+cx: Cx, hs: List<&2, U32>, +n: List<&2, U32>) -> Maybe<&2, U32>:
  match hs:
    case Nil{}:
      None{}
    case Con{+h, t}:
      when(Maybe<&2, U32>, has.def(cx.map(cx, h), n), u => Some{h}, u => look(cx, t, n))

# a dotted name as an object's path and one of its definitions, the
# longest path first; k, the path's length tried
def look.obj(k: Nat, +cx: Cx, +q: U32, +ps: List<&2, List<&2, U32>>) -> Maybe<&2, Rf>:
  match k:
    case 0n:
      None{}
    case 1n++j:
      on.maybe(U32, Maybe<&2, Rf>, resolve(List.length(&2, Ob, cx.obs(cx)), cx.obs(cx), q, List.take(&2, List<&2, U32>, ps, k)),
        u => look.obj(j, cx, q, ps),
        +x => when(Maybe<&2, Rf>, has.def(cx.map(cx, x), dots(List.drop(&2, List<&2, U32>, ps, k))),
          v => Some{Rf{x, dots(List.drop(&2, List<&2, U32>, ps, k)), False{}, x}},
          v => look.obj(j, cx, q, ps)))

def rr.rf(+cx: Cx, +mark: U32, +t: Tok, +no: U32, f: Rf) -> Rr:
  match f:
    case Rf{+obj, +name, +prior, +origin}:
      rr.final(cx, obj, mark, name, t, no)

def rr.dotted(+cx: Cx, +q: U32, +mark: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  on.maybe(Rf, Rr, look.obj(List.length(&2, List<&2, U32>, List.tail(&2, List<&2, U32>, parts(n))), cx, q, parts(n)),
    u => rr.tok(t),
    f => rr.rf(cx, mark, t, no, f))

# a name with no mark, or after `~`: a local, a definition, or Bend's
def rr.plain(+cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +mark: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  when(Rr, names.has(locals, n), u => rr.tok(t),
    u => on.maybe(U32, Rr, look(cx, Con{o, hosts(cx.obs(cx), q)}, n),
      v => rr.dotted(cx, q, mark, n, t, no),
      +h => rr.final(cx, h, mark, n, t, no)))

# the first of the definers, latest first, that comes after q in o's
# linearization
def prior.find(cs: List<&2, U32>, +after: List<&2, U32>) -> Maybe<&2, U32>:
  match cs:
    case Nil{}:
      None{}
    case Con{+c, t}:
      when(Maybe<&2, U32>, has(after, c), u => Some{c}, u => prior.find(t, after))

def after(xs: List<&2, U32>, +q: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      when(List<&2, U32>, U32.is_eq(x, q), u => t, u => after(t, q))

def en.chain(m: Maybe<&2, En>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{e}:
      match e:
        case En{name, chain, +no}:
          chain

# `_n`: the definition of n that q's replaced in o's copy
def rr.prior(+cx: Cx, +o: U32, +q: U32, +n: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  on.maybe(U32, Rr, prior.find(en.chain(en.find(cx.map(cx, o), n)), after(cx.ord(cx, o), q)),
    u => rr.er(t, no, "_" ++ text(n) ++ ": " ++ ob.name(cx.obs(cx), o) ++ " has no definition of " ++ text(n) ++ " before " ++
      ob.name(cx.obs(cx), q) ++ "'s"),
    +c => Rr{RR{0, Rf{o, n, True{}, c}}, Nil{}, [In{n, c, True{}}]})

# `^n`, k carets: the k-th host's final n
def rr.host(+cx: Cx, +q: U32, k: Nat, +n: List<&2, U32>, +t: Tok, +whole: List<&2, U32>, +no: U32) -> Rr:
  on.maybe(U32, Rr, List.get(&2, U32, hosts(cx.obs(cx), q), Nat.sub(k, 1n)),
    u => rr.er(t, no, text(whole) ++ " steps out of the module, which has no host"),
    +h => when(Rr, has.def(cx.map(cx, h), n), v => rr.final(cx, h, 0, n, t, no),
      v => rr.er(t, no, text(whole) ++ ": " ++ ob.name(cx.obs(cx), h) ++ " has no " ++ text(n))))

def rr.mark(+cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +h: U32, +r: List<&2, U32>, +t: Tok, +no: U32) -> Rr:
  match h:
    case 94:
      rr.host(cx, q, carets(Con{h, r}), List.drop(&2, U32, Con{h, r}, carets(Con{h, r})), t, Con{h, r}, no)
    case 126:
      rr.plain(cx, o, q, locals, 126, r, t, no)
    case 95:
      when(Rr, blank(r) || names.has(locals, Con{h, r}), u => rr.tok(t), u => rr.prior(cx, o, q, r, t, no))
    case _:
      rr.plain(cx, o, q, locals, 0, Con{h, r}, t, no)

def rr.of(+cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +t: Tok, +no: U32) -> Rr:
  match t:
    case TName{+x}:
      match x:
        case Nil{}:
          rr.tok(t)
        case Con{+h, +r}:
          rr.mark(cx, o, q, locals, h, r, TName{Con{h, r}}, no)
    case _:
      rr.tok(t)

# A definition's body
# -------------------

type Rb is Data:
  Rb{ls: List<&2, Rl>, ers: List<&2, Er>, ins: List<&2, In>}

def rb.cons(x: Rr, rest: Rb) -> Rb:
  match x rest:
    case Rr{rt, e, i} Rb{ls, es, more}:
      Rb{Con{Rl{0, 0, [rt]}, ls}, List.append(&2, Er, e, es), List.append(&2, In, i, more)}

def rb.toks(ts: List<&2, Tok>, +cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>, +no: U32) -> Rb:
  match ts:
    case Nil{}:
      Rb{Nil{}, Nil{}, Nil{}}
    case Con{t, r}:
      rb.cons(rr.of(cx, o, q, locals, t, no), rb.toks(r, cx, o, q, locals, no))

# a line's tokens, gathered from rb.toks' one-token lines
def rl.join(ls: List<&2, Rl>) -> List<&2, Rt>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Rl{+no, +ind, ts}:
          List.append(&2, Rt, ts, rl.join(t))

def rb.line(+no: U32, +ind: U32, b: Rb) -> Rb:
  match b:
    case Rb{ls, es, more}:
      Rb{[Rl{no, ind, rl.join(ls)}], es, more}

def rb.join(a: Rb, b: Rb) -> Rb:
  match a b:
    case Rb{l1, e1, i1} Rb{l2, e2, i2}:
      Rb{List.append(&2, Rl, l1, l2), List.append(&2, Er, e1, e2), List.append(&2, In, i1, i2)}

def rb.lines(bs: List<&2, Bl>, +cx: Cx, +o: U32, +q: U32, +locals: List<&2, List<&2, U32>>) -> Rb:
  match bs:
    case Nil{}:
      Rb{Nil{}, Nil{}, Nil{}}
    case Con{b, t}:
      match b:
        case Bl{+no, +ind, ts}:
          rb.join(rb.line(no, ind, rb.toks(ts, cx, o, q, locals, no)), rb.lines(t, cx, o, q, locals))

# a body's binders, with the line of each
type Lc is Data:
  Lc{name: List<&2, U32>, +no: U32}

def lc.tag(ns: List<&2, List<&2, U32>>, +no: U32) -> List<&2, Lc>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{Lc{n, no}, lc.tag(t, no)}

def body.binders(bs: List<&2, Bl>) -> List<&2, Lc>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      match b:
        case Bl{+no, +ind, ts}:
          List.append(&2, Lc, lc.tag(line.names(ts), no), body.binders(t))

def lc.names(ls: List<&2, Lc>) -> List<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Lc{n, +no}:
          Con{n, lc.names(t)}

def unmark(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      match h:
        case 126:
          t
        case _:
          Con{h, t}

def unmarks(ns: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{unmark(n), unmarks(t)}

# whether n names a definition a bare name would reach
def visible(+cx: Cx, +o: U32, +q: U32, +n: List<&2, U32>) -> Bool:
  Maybe.is_some(&2, U32, look(cx, Con{o, hosts(cx.obs(cx), q)}, n))

def shadow.params(ps: List<&2, List<&2, U32>>, +cx: Cx, +o: U32, +q: U32, +dn: String, +no: U32) -> List<&2, Er>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, +t}:
      when(List<&2, Er>, visible(cx, o, q, p),
        u => Con{Er{no, "the parameter " ++ text(p) ++ " of " ++ dn ++ " shadows the definition " ++ text(p)}, shadow.params(t, cx, o, q, dn, no)},
        u => shadow.params(t, cx, o, q, dn, no))

def shadow.locals(ls: List<&2, Lc>, +cx: Cx, +o: U32, +q: U32, +dn: String) -> List<&2, Er>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, +t}:
      match l:
        case Lc{+n, +no}:
          when(List<&2, Er>, visible(cx, o, q, n),
            u => Con{Er{no, "the local " ++ text(n) ++ " of " ++ dn ++ " shadows the definition " ++ text(n)}, shadow.locals(t, cx, o, q, dn)},
            u => shadow.locals(t, cx, o, q, dn))

# a resolved definition: what it is, its member as written, its lines
type Rd is Data:
  Rd{inst: In, node: Node, ls: List<&2, Rl>}

# Copies
# ------

def mem.find(ns: List<&2, Node>, +n: List<&2, U32>) -> Maybe<&2, Node>:
  match ns:
    case Nil{}:
      None{}
    case Con{+nd, t}:
      match nd:
        case NDef{+share, +upd, +name, +rest, +params, +body, +no, +ind}:
          when(Maybe<&2, Node>, same(name, n), u => Some{NDef{share, upd, name, rest, params, body, no, ind}}, u => mem.find(t, n))
        case _:
          mem.find(t, n)

def path.name(+path: List<&2, List<&2, U32>>, +n: List<&2, U32>) -> List<&2, U32>:
  match path:
    case Nil{}:
      n
    case Con{h, t}:
      List.append(&2, U32, dots(Con{h, t}), Con{46, n})

# the name a definition is emitted by: `Obj.f`, a prior `Obj.f.Origin`,
# the module's own unprefixed
def rf.text(+obs: List<&2, Ob>, r: Rf) -> List<&2, U32>:
  match r:
    case Rf{+obj, +name, +prior, +origin}:
      when(List<&2, U32>, prior,
        u => List.append(&2, U32, path.name(ob.path(ob.at(obs, obj)), name), Con{46, dots(ob.path(ob.at(obs, origin)))}),
        u => path.name(ob.path(ob.at(obs, obj)), name))

def in.ref(+o: U32, i: In) -> Rf:
  match i:
    case In{name, +q, +prior}:
      Rf{o, name, prior, q}

def copy.k(i: In, nd: Node, b: Rb, sh: List<&2, Er>) -> Rd & Rb:
  match b:
    case Rb{ls, es, more}:
      (Rd{i, nd, ls}, Rb{Nil{}, List.append(&2, Er, sh, es), more})

# a member's copy in o: its body bound, the priors it reaches
def copy.node(+cx: Cx, +o: U32, i: In, +nd: Node) -> Rd & Rb:
  match i:
    case In{+n, +q, +prior}:
      match nd:
        case NDef{+share, +upd, +name, +rest, +params, +body, +no, +ind}:
          copy.k(In{n, q, prior}, nd, rb.lines(body, cx, o, q, List.append(&2, List<&2, U32>, unmarks(params), lc.names(body.binders(body)))),
            List.append(&2, Er, shadow.params(unmarks(params), cx, o, q, text(rf.text(cx.obs(cx), in.ref(o, In{n, q, prior}))), no),
              shadow.locals(body.binders(body), cx, o, q, text(rf.text(cx.obs(cx), in.ref(o, In{n, q, prior}))))))
        case _:
          (Rd{In{n, q, prior}, nd, Nil{}}, Rb{Nil{}, Nil{}, Nil{}})

def copy.of(+cx: Cx, +o: U32, +i: In) -> Rd & Rb:
  match i:
    case In{+n, +q, +prior}:
      on.maybe(Node, Rd & Rb, mem.find(ob.mems(ob.at(cx.obs(cx), q)), n),
        u => (Rd{i, NBad{Nil{}, 0}, Nil{}}, Rb{Nil{}, Nil{}, Nil{}}),
        nd => copy.node(cx, o, i, nd))

def in.eq(a: In, b: In) -> Bool:
  match a b:
    case In{n, +q, +p} In{m, +r, +s}:
      same(n, m) && U32.is_eq(q, r) && Bool.not(Bool.xor(p, s))

def ins.has(+xs: List<&2, In>, +i: In) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{+x, t}:
      in.eq(x, i) || ins.has(t, i)

# the copies made so far, their errors
type Cp is Data:
  Cp{rds: List<&2, Rd>, ers: List<&2, Er>, done: List<&2, In>}

def on.pair(-A: Type, -B: Type, -R: Type, p: A & B, f: A -> B -> R) -> R:
  (a, b) = p
  f(a, b)

def cp.add(rd: Rd, b: Rb, c: Cp) -> Cp:
  match b c:
    case Rb{ls, es, more} Cp{rds, ers, done}:
      Cp{Con{rd, rds}, List.append(&2, Er, ers, es), done}

def rb.ins(b: Rb) -> List<&2, In>:
  match b:
    case Rb{ls, es, more}:
      more

# the worklist of copies: the finals, then each prior reached; fuel, the
# file's definitions
def copies.go(n: Nat, +cx: Cx, +o: U32, todo: List<&2, In>, +c: Cp) -> Cp:
  match n:
    case 0n:
      c
    case 1n++k:
      match todo:
        case Nil{}:
          c
        case Con{+i, +t}:
          match c:
            case Cp{+rds, +ers, +done}:
              when(Cp, ins.has(done, i), u => copies.go(k, cx, o, t, Cp{rds, ers, done}),
                u => on.pair(Rd, Rb, Cp, copy.of(cx, o, i),
                  rd => +b => copies.go(k, cx, o, List.append(&2, In, t, rb.ins(b)), cp.add(rd, b, Cp{rds, ers, Con{i, done}}))))

def ins.finals(es: List<&2, En>) -> List<&2, In>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      match e:
        case En{name, chain, +no}:
          Con{In{name, en.head(chain), False{}}, ins.finals(t)}

# a concrete object's copies: its finals, then each prior they reach
def copies(+cx: Cx, +o: U32) -> Cp:
  copies.go(1n+count(ob.mems(ob.at(cx.obs(cx), 0))), cx, o, ins.finals(cx.map(cx, o)), Cp{Nil{}, Nil{}, Nil{}})

# The copies, printed
# -------------------

def show.rts(+obs: List<&2, Ob>, ts: List<&2, Rt>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, r}:
      match t:
        case RR{+mark, ref}:
          Con{text(rf.text(obs, ref)), show.rts(obs, r)}
        case _:
          show.rts(obs, r)

def show.rls(+obs: List<&2, Ob>, ls: List<&2, Rl>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Rl{+no, +ind, ts}:
          List.append(&2, String, show.rts(obs, ts), show.rls(obs, t))

def show.strs(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match t:
        case Nil{}:
          x
        case Con{h, r}:
          x ++ ", " ++ show.strs(Con{h, r})

def show.refs(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      " -> " ++ show.strs(Con{x, t})

def show.rds(+obs: List<&2, Ob>, +o: U32, rs: List<&2, Rd>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, t}:
      match r:
        case Rd{i, nd, ls}:
          "  " ++ text(rf.text(obs, in.ref(o, i))) ++ show.refs(show.rls(obs, ls)) ++ "\n" ++ show.rds(obs, o, t)

# A module's copies
# -----------------

def cp.ers(c: Cp) -> List<&2, Er>:
  match c:
    case Cp{rds, ers, done}:
      ers

def cp.rds(c: Cp) -> List<&2, Rd>:
  match c:
    case Cp{rds, ers, done}:
      List.reverse(&2, Rd, rds)

# a concrete object and its copies
type Oc is Data:
  Oc{+id: U32, cp: Cp}

# every concrete object's copies, the module's first
def module.copies(os: List<&2, Ob>, +cx: Cx) -> List<&2, Oc>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, path, +abs, parents, mems, +no}:
          when(List<&2, Oc>, abs, u => module.copies(t, cx), u => Con{Oc{id, copies(cx, id)}, module.copies(t, cx)})

def ocs.ers(os: List<&2, Oc>) -> List<&2, Er>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      match o:
        case Oc{+id, c}:
          List.append(&2, Er, cp.ers(c), ocs.ers(t))

def show.ocs(+obs: List<&2, Ob>, os: List<&2, Oc>) -> String:
  match os:
    case Nil{}:
      ""
    case Con{o, t}:
      match o:
        case Oc{+id, c}:
          ob.name(obs, id) ++ "\n" ++ show.rds(obs, id, cp.rds(c)) ++ show.ocs(obs, t)

def er.same(a: Er, b: Er) -> Bool:
  match a b:
    case Er{+x, m} Er{+y, n}:
      U32.is_eq(x, y) && String.eq(m, n)

# sorted errors, each once: a body copied into several objects may raise
# one error in each
def ers.uniq(es: List<&2, Er>) -> List<&2, Er>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      match t:
        case Nil{}:
          [e]
        case Con{+f, +r}:
          when(List<&2, Er>, er.same(e, f), u => ers.uniq(Con{f, r}), u => Con{e, ers.uniq(Con{f, r})})

# a command's output: what it printed, and whether it found no error
type Out is Type:
  Out{+ok: Bool, text: String}

def ers.out(+file: String, es: List<&2, Er>) -> Out:
  Out{False{}, show.ers(file, ers.uniq(List.sort(~Er, ~er.le, es)))}

def resolve.out(+file: String, +obs: List<&2, Ob>, +os: List<&2, Oc>, es: List<&2, Er>) -> Out:
  match es:
    case Nil{}:
      Out{True{}, show.ocs(obs, os)}
    case Con{e, t}:
      ers.out(file, Con{e, t})

def resolved(+file: String, +obs: List<&2, Ob>, +os: List<&2, Oc>) -> Out:
  resolve.out(file, obs, os, ocs.ers(os))

# Emission
# ========
#
# The emitted module (`blend-emit`): every copy a unit, the units in
# source order (the module's definitions and its concrete objects by
# their lines, an object's members in its linearization's order, its own
# first), emitted callees first by a walk from each in turn, or from the
# roots the command line names; two units calling each other an error,
# as Bend has no mutual recursion (`blend-adds-no-bend-logic`). Then the
# sharing: an affine unit has one use at most, a call to itself aside; a
# copied unit is emitted once for each use, `Obj.f.c1` and on in the
# order the uses are emitted, and an affine unit only a multiplied unit
# uses goes with each of its copies, numbered alike.

# a unit: one definition of the emitted program, before copies, and the
# concrete object it is emitted in
type Un is Data:
  Un{+o: U32, inst: In, node: Node, ls: List<&2, Rl>}

def rf.eq(a: Rf, b: Rf) -> Bool:
  match a b:
    case Rf{+o1, n1, +p1, +g1} Rf{+o2, n2, +p2, +g2}:
      U32.is_eq(o1, o2) && same(n1, n2) && Bool.not(Bool.xor(p1, p2)) && (Bool.not(p1) || U32.is_eq(g1, g2))

def un.rds(+o: U32, rs: List<&2, Rd>) -> List<&2, Un>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case Rd{i, nd, ls}:
          Con{Un{o, i, nd, ls}, un.rds(o, t)}

def units(os: List<&2, Oc>) -> List<&2, Un>:
  match os:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match x:
        case Oc{+id, c}:
          List.append(&2, Un, un.rds(id, cp.rds(c)), units(t))

def un.ref(u: Un) -> Rf:
  match u:
    case Un{+o, i, nd, ls}:
      in.ref(o, i)

def un.node(u: Un) -> Node:
  match u:
    case Un{+o, i, nd, ls}:
      nd

def un.lines(u: Un) -> List<&2, Rl>:
  match u:
    case Un{+o, i, nd, ls}:
      ls

def un.or(m: Maybe<&2, Un>) -> Un:
  match m:
    case None{}:
      Un{0, In{Nil{}, 0, False{}}, NBad{Nil{}, 0}, Nil{}}
    case Some{u}:
      u

def un.at(+us: List<&2, Un>, +i: U32) -> Un:
  un.or(List.get(&2, Un, us, U32.to_nat(i)))

# a unit's index
def un.find(+us: List<&2, Un>, +r: Rf, +k: U32) -> Maybe<&2, U32>:
  match us:
    case Nil{}:
      None{}
    case Con{+u, +t}:
      when(Maybe<&2, U32>, rf.eq(un.ref(u), r), v => Some{k}, v => un.find(t, r, (k + 1 : U32)))

def node.no(n: Node) -> U32:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind}:
      no
    case _:
      0

def node.ind(n: Node) -> U32:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind}:
      ind
    case _:
      0

def node.share(n: Node) -> U32:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind}:
      share
    case _:
      0

def node.rest(n: Node) -> List<&2, U32>:
  match n:
    case NDef{+share, +upd, name, rest, params, body, +no, +ind}:
      rest
    case _:
      Nil{}

def un.name(+obs: List<&2, Ob>, +us: List<&2, Un>, +i: U32) -> List<&2, U32>:
  rf.text(obs, un.ref(un.at(us, i)))

# Uses
# ----

# a use: the unit used or using, and the line
type Ru is Data:
  Ru{+u: U32, +no: U32}

def refs.rts(ts: List<&2, Rt>, +us: List<&2, Un>, +self: U32, +no: U32) -> List<&2, Ru>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, +r}:
      match t:
        case RR{+mark, ref}:
          on.maybe(U32, List<&2, Ru>, un.find(us, ref, 0), v => refs.rts(r, us, self, no),
            +x => when(List<&2, Ru>, U32.is_eq(x, self), v => refs.rts(r, us, self, no), v => Con{Ru{x, no}, refs.rts(r, us, self, no)}))
        case _:
          refs.rts(r, us, self, no)

def refs.rls(ls: List<&2, Rl>, +us: List<&2, Un>, +self: U32) -> List<&2, Ru>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, t}:
      match l:
        case Rl{+no, +ind, ts}:
          List.append(&2, Ru, refs.rts(ts, us, self, no), refs.rls(t, us, self))

# each unit's uses of others, in its body's order, calls to itself aside
def refss(xs: List<&2, Un>, +us: List<&2, Un>, +k: U32) -> List<&2, List<&2, Ru>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{refs.rls(un.lines(x), us, k), refss(t, us, (k + 1 : U32))}

def ru.us(rs: List<&2, Ru>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      match r:
        case Ru{+u, +no}:
          Con{u, ru.us(t)}

def calls(rss: List<&2, List<&2, Ru>>) -> List<&2, List<&2, U32>>:
  match rss:
    case Nil{}:
      Nil{}
    case Con{rs, t}:
      Con{ru.us(rs), calls(t)}

def ids.or(m: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      x

def ids.at(+xss: List<&2, List<&2, U32>>, +i: U32) -> List<&2, U32>:
  ids.or(List.get(&2, List<&2, U32>, xss, U32.to_nat(i)))

def rus.or(m: Maybe<&2, List<&2, Ru>>) -> List<&2, Ru>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      x

def rus.at(+rss: List<&2, List<&2, Ru>>, +i: U32) -> List<&2, Ru>:
  rus.or(List.get(&2, List<&2, Ru>, rss, U32.to_nat(i)))

# Order
# -----

# the units a source-order slot holds: a definition of the module's, or a
# concrete object
type Sl is Data:
  Sl{+no: U32, +kind: U32, name: List<&2, U32>, +id: U32}

def sl.le(a: Sl, b: Sl) -> Bool:
  match a b:
    case Sl{+x, +k1, n1, +i1} Sl{+y, +k2, n2, +i2}:
      U32.is_le(x, y)

def slots.mod(ns: List<&2, Node>) -> List<&2, Sl>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, t}:
      match nd:
        case NDef{+share, +upd, name, rest, params, body, +no, +ind}:
          Con{Sl{no, 0, name, 0}, slots.mod(t)}
        case _:
          slots.mod(t)

def slots.obs(os: List<&2, Ob>) -> List<&2, Sl>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, +t}:
      match o:
        case Ob{+id, +host, path, +abs, parents, mems, +no}:
          when(List<&2, Sl>, abs || U32.is_eq(id, 0), u => slots.obs(t), u => Con{Sl{no, 1, Nil{}, id}, slots.obs(t)})

# q's members that are o's finals, as references
def roots.q(ns: List<&2, Node>, +o: U32, +q: U32, +map: List<&2, En>) -> List<&2, Rf>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, +t}:
      match nd:
        case NDef{+share, +upd, +name, rest, params, body, +no, +ind}:
          when(List<&2, Rf>, U32.is_eq(en.head(en.chain(en.find(map, name))), q),
            u => Con{Rf{o, name, False{}, o}, roots.q(t, o, q, map)}, u => roots.q(t, o, q, map))
        case _:
          roots.q(t, o, q, map)

def roots.ord(qs: List<&2, U32>, +cx: Cx, +o: U32) -> List<&2, Rf>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{+q, t}:
      List.append(&2, Rf, roots.q(ob.mems(ob.at(cx.obs(cx), q)), o, q, cx.map(cx, o)), roots.ord(t, cx, o))

def roots.sl(s: Sl, +cx: Cx) -> List<&2, Rf>:
  match s:
    case Sl{+no, +kind, name, +id}:
      match kind:
        case 0:
          [Rf{0, name, False{}, 0}]
        case _:
          roots.ord(cx.ord(cx, id), cx, id)

def roots.sls(ss: List<&2, Sl>, +cx: Cx) -> List<&2, Rf>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      List.append(&2, Rf, roots.sl(s, cx), roots.sls(t, cx))

def roots.ids(rs: List<&2, Rf>, +us: List<&2, Un>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, +t}:
      on.maybe(U32, List<&2, U32>, un.find(us, r, 0), u => roots.ids(t, us), x => Con{x, roots.ids(t, us)})

# every unit in source order
def roots.all(+cx: Cx, +us: List<&2, Un>) -> List<&2, U32>:
  roots.ids(roots.sls(List.sort(~Sl, ~sl.le, List.append(&2, Sl, slots.mod(ob.mems(ob.at(cx.obs(cx), 0))), slots.obs(cx.obs(cx)))), cx), us)

def un.named(+obs: List<&2, Ob>, +us: List<&2, Un>, +n: List<&2, U32>, +k: U32) -> Maybe<&2, U32>:
  match us:
    case Nil{}:
      None{}
    case Con{+u, +t}:
      when(Maybe<&2, U32>, same(rf.text(obs, un.ref(u)), n), v => Some{k}, v => un.named(obs, t, n, (k + 1 : U32)))

# roots named on the command line, by their emitted names
def roots.named(rs: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, +t}:
      on.maybe(U32, List<&2, U32>, un.named(obs, us, r, 0), u => roots.named(t, obs, us), x => Con{x, roots.named(t, obs, us)})

def er.roots(rs: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> List<&2, Er>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{+r, +t}:
      on.maybe(U32, List<&2, Er>, un.named(obs, us, r, 0),
        u => Con{Er{0, "the root " ++ text(r) ++ " names no definition"}, er.roots(t, obs, us)},
        x => er.roots(t, obs, us))

# The walk
# --------

# a unit being walked, and its calls not yet followed
type Fm is Data:
  Fm{+u: U32, rest: List<&2, U32>}

# the walk: its stack, the roots left, the units on the stack (the top
# first), those done, the order (the last first), its errors
type Ds is Data:
  Ds{stack: List<&2, Fm>, roots: List<&2, U32>, path: List<&2, U32>, done: List<&2, U32>, order: List<&2, U32>, ers: List<&2, Er>}

def path.to(ps: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      when(List<&2, U32>, U32.is_eq(p, c), u => [p], u => Con{p, path.to(t, c)})

def strs.and(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, t}:
      match t:
        case Nil{}:
          x
        case Con{y, r}:
          match r:
            case Nil{}:
              x ++ " and " ++ y
            case Con{z, r2}:
              x ++ ", " ++ strs.and(Con{y, Con{z, r2}})

def unit.names(xs: List<&2, U32>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{text(un.name(obs, us, x)), unit.names(t, obs, us)}

# units that call each other: those on the stack from c to the top
def er.cycle(+obs: List<&2, Ob>, +us: List<&2, Un>, +path: List<&2, U32>, +c: U32) -> Er:
  Er{node.no(un.node(un.at(us, c))),
    strs.and(unit.names(List.reverse(&2, U32, path.to(path, c)), obs, us)) ++ " call each other, which Bend cannot express"}

def ds.call(+c: U32, +u: U32, +rs: List<&2, U32>, +st: List<&2, Fm>, +roots: List<&2, U32>, +path: List<&2, U32>, +done: List<&2, U32>,
    +order: List<&2, U32>, +ers: List<&2, Er>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  when(Ds, has(done, c), v => Ds{Con{Fm{u, rs}, st}, roots, path, done, order, ers},
    v => when(Ds, has(path, c), w => Ds{Con{Fm{u, rs}, st}, roots, path, done, order, Con{er.cycle(obs, us, path, c), ers}},
      w => Ds{Con{Fm{c, ids.at(cal, c)}, Con{Fm{u, rs}, st}}, roots, Con{c, path}, done, order, ers}))

def ds.step(s: Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  match s:
    case Ds{stack, roots, path, +done, +order, +ers}:
      match stack:
        case Nil{}:
          match roots:
            case Nil{}:
              Ds{Nil{}, Nil{}, path, done, order, ers}
            case Con{+r, +rt}:
              when(Ds, has(done, r), u => Ds{Nil{}, rt, path, done, order, ers},
                u => Ds{[Fm{r, ids.at(cal, r)}], rt, [r], done, order, ers})
        case Con{f, st}:
          match f:
            case Fm{+u, rest}:
              match rest:
                case Nil{}:
                  Ds{st, roots, List.tail(&2, U32, path), Con{u, done}, Con{u, order}, ers}
                case Con{+c, rs}:
                  ds.call(c, u, rs, st, roots, path, done, order, ers, cal, obs, us)

def ds.go(n: Nat, s: Ds, +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  match n:
    case 0n:
      s
    case 1n+k:
      ds.go(k, ds.step(s, cal, obs, us), cal, obs, us)

def lens(xss: List<&2, List<&2, U32>>) -> Nat:
  match xss:
    case Nil{}:
      0n
    case Con{xs, t}:
      Nat.add(List.length(&2, U32, xs), lens(t))

# the walk from the roots: each step pushes, pops or follows a call
def walk(+roots: List<&2, U32>, +cal: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +us: List<&2, Un>) -> Ds:
  ds.go(Nat.add(Nat.add(List.length(&2, U32, roots), lens(cal)), Nat.add(List.length(&2, Un, us), List.length(&2, Un, us))),
    Ds{Nil{}, roots, Nil{}, Nil{}, Nil{}, Nil{}}, cal, obs, us)

# Sharing
# -------

# how a unit is emitted: m copies, plain (0), numbered by its uses
# (copied, 1) or by its one user's copies (2)
type Mu is Data:
  Mu{+m: U32, +kind: U32}

def mu.or(x: Maybe<&2, Mu>) -> Mu:
  match x:
    case None{}:
      Mu{1, 0}
    case Some{v}:
      v

def mu.at(+ms: List<&2, Mu>, +i: U32) -> Mu:
  mu.or(List.get(&2, Mu, ms, U32.to_nat(i)))

def mu.m(x: Mu) -> U32:
  match x:
    case Mu{+m, +kind}:
      m

def mu.kind(x: Mu) -> U32:
  match x:
    case Mu{+m, +kind}:
      kind

def uses.in(rs: List<&2, Ru>, +e: U32, +x: U32) -> List<&2, Ru>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, +t}:
      match r:
        case Ru{+u, +no}:
          when(List<&2, Ru>, U32.is_eq(u, x), v => Con{Ru{e, no}, uses.in(t, e, x)}, v => uses.in(t, e, x))

# the uses of x by the emitted units, in their order
def uses.of(es: List<&2, U32>, +rss: List<&2, List<&2, Ru>>, +x: U32) -> List<&2, Ru>:
  match es:
    case Nil{}:
      Nil{}
    case Con{+e, t}:
      List.append(&2, Ru, uses.in(rus.at(rss, e), e, x), uses.of(t, rss, x))

def uses.m(us: List<&2, Ru>, +ms: List<&2, Mu>) -> U32:
  match us:
    case Nil{}:
      0
    case Con{r, t}:
      match r:
        case Ru{+u, +no}:
          (mu.m(mu.at(ms, u)) + uses.m(t, ms) : U32)

def ru.user(rs: List<&2, Ru>) -> U32:
  match rs:
    case Nil{}:
      0
    case Con{r, t}:
      match r:
        case Ru{+u, +no}:
          u

def times(+n: U32) -> String:
  match n:
    case 1:
      ""
    case 2:
      ", twice"
    case _:
      ", " ++ U32.show(n) ++ " times"

# the uses grouped by user and line: `Obj.f (line 9, twice)`
def uses.say(rs: List<&2, Ru>, +obs: List<&2, Ob>, +us: List<&2, Un>, +u: U32, +no: U32, +n: U32) -> List<&2, String>:
  match rs:
    case Nil{}:
      when(List<&2, String>, U32.is_eq(n, 0), v => Nil{},
        v => [text(un.name(obs, us, u)) ++ " (line " ++ U32.show(no) ++ times(n) ++ ")"])
    case Con{r, +t}:
      match r:
        case Ru{+v, +l}:
          when(List<&2, String>, (U32.is_eq(v, u) && U32.is_eq(l, no)) || U32.is_eq(n, 0), w => uses.say(t, obs, us, v, l, (n + 1 : U32)),
            w => Con{text(un.name(obs, us, u)) ++ " (line " ++ U32.show(no) ++ times(n) ++ ")", uses.say(t, obs, us, v, l, 1)})

def er.affine(+obs: List<&2, Ob>, +us: List<&2, Un>, +x: U32, +rs: List<&2, Ru>) -> Er:
  Er{node.no(un.node(un.at(us, x))), text(un.name(obs, us, x)) ++ " is affine and has " ++ U32.show(U32.from_nat(List.length(&2, Ru, rs))) ++
    " uses, in " ++ show.strs(uses.say(rs, obs, us, 0, 0, 0)) ++ ": mark it shared or copied"}

type Ms is Data:
  Ms{ms: List<&2, Mu>, ers: List<&2, Er>}

def ms.set(s: Ms, +x: U32, +mu: Mu) -> Ms:
  match s:
    case Ms{ms, ers}:
      Ms{List.set(&2, Mu, ms, U32.to_nat(x), mu), ers}

def ms.er(s: Ms, e: Er) -> Ms:
  match s:
    case Ms{ms, ers}:
      Ms{ms, Con{e, ers}}

def ms.ms(s: Ms) -> List<&2, Mu>:
  match s:
    case Ms{ms, ers}:
      ms

# an affine unit: plain when unused, the copies of its one user, an error
# when used twice
def mult.aff(n: Nat, +x: U32, +rs: List<&2, Ru>, +obs: List<&2, Ob>, +us: List<&2, Un>, +s: Ms) -> Ms:
  match n:
    case 0n:
      s
    case 1n+k:
      match k:
        case 0n:
          when(Ms, U32.is_gt(mu.m(mu.at(ms.ms(s), ru.user(rs))), 1), v => ms.set(s, x, Mu{mu.m(mu.at(ms.ms(s), ru.user(rs))), 2}), v => s)
        case _:
          ms.er(s, er.affine(obs, us, x, rs))

# x's copies, its users' known: a copied unit's uses, an affine unit's one
# user's copies, an affine unit used twice an error
def mult.of(+x: U32, +share: U32, +rs: List<&2, Ru>, +obs: List<&2, Ob>, +us: List<&2, Un>, +s: Ms) -> Ms:
  match share:
    case 1:
      s
    case 2:
      when(Ms, U32.is_eq(uses.m(rs, ms.ms(s)), 0), v => s, v => ms.set(s, x, Mu{uses.m(rs, ms.ms(s)), 1}))
    case _:
      mult.aff(List.length(&2, Ru, rs), x, rs, obs, us, s)

# from the last emitted to the first: each unit's users before it
def mults(xs: List<&2, U32>, +es: List<&2, U32>, +rss: List<&2, List<&2, Ru>>, +obs: List<&2, Ob>, +us: List<&2, Un>, s: Ms) -> Ms:
  match xs:
    case Nil{}:
      s
    case Con{+x, t}:
      mults(t, es, rss, obs, us, mult.of(x, node.share(un.node(un.at(us, x))), uses.of(es, rss, x), obs, us, s))

def mus.one(us: List<&2, Un>) -> List<&2, Mu>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, t}:
      Con{Mu{1, 0}, mus.one(t)}

# Text
# ----

# what emission reads: the objects, the units, how each is emitted
type Ec is Data:
  Ec{obs: List<&2, Ob>, us: List<&2, Un>, mus: List<&2, Mu>}

def ec.obs(e: Ec) -> List<&2, Ob>:
  match e:
    case Ec{obs, us, mus}:
      obs

def ec.us(e: Ec) -> List<&2, Un>:
  match e:
    case Ec{obs, us, mus}:
      us

def ec.mu(e: Ec, +i: U32) -> Mu:
  match e:
    case Ec{obs, us, mus}:
      mu.at(mus, i)

# the text so far, its bytes reversed, and each copied unit's next number
type Tb is Data:
  Tb{acc: List<&2, U32>, ctrs: List<&2, U32>}

def rev.onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev.onto(t, Con{h, acc})

def tb.put(b: Tb, xs: List<&2, U32>) -> Tb:
  match b:
    case Tb{acc, ctrs}:
      Tb{rev.onto(xs, acc), ctrs}

def tok.bytes(t: Tok) -> List<&2, U32>:
  match t:
    case TName{x}:
      x
    case TNum{x}:
      x
    case TStr{x}:
      x
    case TCom{x}:
      x
    case TSp{x}:
      x
    case TSym{+c}:
      [c]

def copy.name(base: List<&2, U32>, +j: U32) -> List<&2, U32>:
  List.append(&2, U32, base, List.append(&2, U32, codes(".c"), codes(U32.show(j))))

def unit.text(+e: Ec, +x: U32) -> List<&2, U32>:
  un.name(ec.obs(e), ec.us(e), x)

# a unit's own name in its j-th copy
def own.name(+e: Ec, +x: U32, +j: U32) -> List<&2, U32>:
  when(List<&2, U32>, U32.is_eq(mu.kind(ec.mu(e, x)), 0), u => unit.text(e, x), u => copy.name(unit.text(e, x), j))

def ctr.or(m: Maybe<&2, U32>) -> U32:
  match m:
    case None{}:
      1
    case Some{+x}:
      x

def ctr.at(+cs: List<&2, U32>, +i: U32) -> U32:
  ctr.or(List.get(&2, U32, cs, U32.to_nat(i)))

# a use of y from the j-th copy: plain, the next of y's copies, or the
# copy of y that goes with the user's j-th
def ref.kind(+kind: U32, +e: Ec, +y: U32, +j: U32, b: Tb) -> Tb:
  match kind:
    case 0:
      tb.put(b, unit.text(e, y))
    case 1:
      match b:
        case Tb{acc, +ctrs}:
          Tb{rev.onto(copy.name(unit.text(e, y), ctr.at(ctrs, y)), acc), List.set(&2, U32, ctrs, U32.to_nat(y), (ctr.at(ctrs, y) + 1 : U32))}
    case _:
      tb.put(b, copy.name(unit.text(e, y), j))

def ref.self(+self: Bool, +e: Ec, +x: U32, +j: U32, +y: U32, b: Tb) -> Tb:
  match self:
    case True{}:
      tb.put(b, own.name(e, x, j))
    case False{}:
      ref.kind(mu.kind(ec.mu(e, y)), e, y, j, b)

def mark.put(+mark: U32, b: Tb) -> Tb:
  match mark:
    case 126:
      tb.put(b, [126])
    case _:
      b

def ref.put(+e: Ec, +x: U32, +j: U32, +mark: U32, m: Maybe<&2, U32>, b: Tb) -> Tb:
  match m:
    case None{}:
      b
    case Some{+y}:
      ref.self(U32.is_eq(y, x), e, x, j, y, mark.put(mark, b))

def rts.put(ts: List<&2, Rt>, +e: Ec, +x: U32, +j: U32, b: Tb) -> Tb:
  match ts:
    case Nil{}:
      b
    case Con{t, r}:
      match t:
        case RT{tk}:
          rts.put(r, e, x, j, tb.put(b, tok.bytes(tk)))
        case RR{+mark, ref}:
          rts.put(r, e, x, j, ref.put(e, x, j, mark, un.find(ec.us(e), ref, 0), b))

def spaces(n: Nat) -> List<&2, U32>:
  List.replicate(U32, n, 32)

# a body line, its indentation the definition's subtracted
def rl.put(l: Rl, +e: Ec, +x: U32, +j: U32, +dind: U32, b: Tb) -> Tb:
  match l:
    case Rl{+no, +ind, ts}:
      match ts:
        case Nil{}:
          tb.put(b, [10])
        case Con{t, r}:
          rts.put(Con{t, r}, e, x, j,
            tb.put(b, Con{10, spaces(U32.to_nat(when(U32, U32.is_gt(ind, dind), u => (ind - dind : U32), u => 0)))}))

def rls.put(ls: List<&2, Rl>, +e: Ec, +x: U32, +j: U32, +dind: U32, b: Tb) -> Tb:
  match ls:
    case Nil{}:
      b
    case Con{l, t}:
      rls.put(t, e, x, j, dind, rl.put(l, e, x, j, dind, b))

# a definition's j-th copy, after a blank line: `def NAME(...) -> T:` and
# its body
def unit.put(+e: Ec, +x: U32, +j: U32, b: Tb) -> Tb:
  tb.put(rls.put(un.lines(un.at(ec.us(e), x)), e, x, j, node.ind(un.node(un.at(ec.us(e), x))),
    tb.put(b, List.append(&2, U32, codes("\ndef "), List.append(&2, U32, own.name(e, x, j), node.rest(un.node(un.at(ec.us(e), x))))))),
    [10])

def copies.put(n: Nat, +e: Ec, +x: U32, +j: U32, b: Tb) -> Tb:
  match n:
    case 0n:
      b
    case 1n+k:
      copies.put(k, e, x, (j + 1 : U32), unit.put(e, x, j, b))

def unit.all(+e: Ec, +x: U32, +mu: Mu, b: Tb) -> Tb:
  match mu:
    case Mu{+m, +kind}:
      match kind:
        case 0:
          unit.put(e, x, 0, b)
        case _:
          copies.put(U32.to_nat(m), e, x, 1, b)

def order.put(xs: List<&2, U32>, +e: Ec, b: Tb) -> Tb:
  match xs:
    case Nil{}:
      b
    case Con{+x, t}:
      order.put(t, e, unit.all(e, x, ec.mu(e, x), b))

def imports(ns: List<&2, Node>) -> List<&2, U32>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{nd, t}:
      match nd:
        case NImport{txt, +no}:
          List.append(&2, U32, txt, Con{10, imports(t)})
        case _:
          imports(t)

# bytes as UTF-8, to the String printed; need, the continuation bytes
# still due, cp the code point so far
def utf8(xs: List<&2, U32>, +need: U32, +cp: U32) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{+b, +t}:
      when(String, U32.is_gt(need, 0),
        u => when(String, U32.is_eq(need, 1),
          v => SCon{Char.from_u32(((cp << 6n) .|. (b .&. 63) : U32)), utf8(t, 0, 0)},
          v => utf8(t, (need - 1 : U32), ((cp << 6n) .|. (b .&. 63) : U32))),
        u => when(String, U32.is_lt(b, 128), v => SCon{Char.from_u32(b), utf8(t, 0, 0)},
          v => when(String, U32.is_lt(b, 224), w => utf8(t, 1, (b .&. 31 : U32)),
            w => when(String, U32.is_lt(b, 240), z => utf8(t, 2, (b .&. 15 : U32)), z => utf8(t, 3, (b .&. 7 : U32))))))

def zeros(us: List<&2, Un>) -> List<&2, U32>:
  match us:
    case Nil{}:
      Nil{}
    case Con{u, t}:
      Con{1, zeros(t)}

def tb.text(b: Tb) -> String:
  match b:
    case Tb{acc, ctrs}:
      utf8(List.reverse(&2, U32, List.tail(&2, U32, acc)), 0, 0)

# the emitted module: its header, Bend's imports, each unit's copies in
# order, the last newline left to IO.print
def module.text(+file: String, +e: Ec, +order: List<&2, U32>, +tree: List<&2, Node>) -> String:
  tb.text(order.put(order, e, Tb{rev.onto(List.append(&2, U32, codes("# Written by Blend from " ++ file ++ "; do not edit.\n"),
    imports(tree)), Nil{}), zeros(ec.us(e))}))

def ds.order(d: Ds) -> List<&2, U32>:
  match d:
    case Ds{stack, roots, path, done, order, ers}:
      order

def ds.ers(d: Ds) -> List<&2, Er>:
  match d:
    case Ds{stack, roots, path, done, order, ers}:
      ers

def ms.ers(s: Ms) -> List<&2, Er>:
  match s:
    case Ms{ms, ers}:
      ers

def roots.of(rs: List<&2, List<&2, U32>>, +cx: Cx, +us: List<&2, Un>) -> List<&2, U32>:
  match rs:
    case Nil{}:
      roots.all(cx, us)
    case Con{r, t}:
      roots.named(Con{r, t}, cx.obs(cx), us)

def emit.out(+file: String, +e: Ec, +order: List<&2, U32>, +tree: List<&2, Node>, es: List<&2, Er>) -> Out:
  match es:
    case Nil{}:
      Out{True{}, module.text(file, e, List.reverse(&2, U32, order), tree)}
    case Con{x, t}:
      ers.out(file, Con{x, t})

# the emitted module, or its errors
def emitted(+file: String, +roots: List<&2, List<&2, U32>>, +cx: Cx, +os: List<&2, Oc>) -> Out:
  +obs = cx.obs(cx)
  +us = units(os)
  +rss = refss(us, us, 0)
  +d = walk(roots.of(roots, cx, us), calls(rss), obs, us)
  +order = ds.order(d)
  +ms = mults(order, List.reverse(&2, U32, order), rss, obs, us, Ms{mus.one(us), Nil{}})
  emit.out(file, Ec{obs, us, ms.ms(ms)}, order, ob.mems(ob.at(obs, 0)),
    List.append(&2, Er, er.roots(roots, obs, us), List.append(&2, Er, ds.ers(d), ms.ers(ms))))

# Stages
# ======
#
# A stage runs when the one before it found no error: the objects, the
# references, then emission.

def resolved.next(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, +cx: Cx, +os: List<&2, Oc>) -> Out:
  match cmd:
    case 3:
      resolved(file, cx.obs(cx), os)
    case _:
      when(Out, Maybe.is_some(&2, Er, List.head(&2, Er, ocs.ers(os))), u => resolved(file, cx.obs(cx), os), u => emitted(file, roots, cx, os))

def objects.next(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +ls: List<&2, Maybe<&2, Lz>>, +fs: List<&2, Maybe<&2, Fd>>) -> Out:
  match cmd:
    case 2:
      Out{True{}, show.obs(obs, ls, fs, obs)}
    case _:
      resolved.next(cmd, file, roots, Cx{obs, ls, fs}, module.copies(obs, Cx{obs, ls, fs}))

def objects.out(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +ls: List<&2, Maybe<&2, Lz>>, +fs: List<&2, Maybe<&2, Fd>>, es: List<&2, Er>) -> Out:
  match es:
    case Nil{}:
      objects.next(cmd, file, roots, obs, ls, fs)
    case Con{e, t}:
      ers.out(file, Con{e, t})

def objects.k(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +pss: List<&2, List<&2, U32>>, +ls: List<&2, Maybe<&2, Lz>>, +fs: List<&2, Maybe<&2, Fd>>) -> Out:
  objects.out(cmd, file, roots, obs, ls, fs,
    List.append(&2, Er, er.obs(obs, obs), List.append(&2, Er, er.lins(pss, ls, 0, obs, ls), er.defs(pss, fs, ls, 0, obs, fs))))

def objects.l(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +pss: List<&2, List<&2, U32>>, +ls: List<&2, Maybe<&2, Lz>>) -> Out:
  objects.k(cmd, file, roots, obs, pss, ls, folds(ls, obs))

def objects.p(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, +obs: List<&2, Ob>, +pss: List<&2, List<&2, U32>>) -> Out:
  objects.l(cmd, file, roots, obs, pss, lins(pss))

def objects.o(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, +obs: List<&2, Ob>) -> Out:
  objects.p(cmd, file, roots, obs, pids(obs, obs))

# the module's objects (cmd 2), their copies (3) or the emitted module
# (4), or the errors of the first stage that has them, each
# `FILE:LINE: message`
def objects(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, +tree: List<&2, Node>) -> Out:
  objects.o(cmd, file, roots, obs(tree))

# The command line
# ================
#
#   bend blend.bend read FILE.blend       the structure (`blend-read`)
#   bend blend.bend objects FILE.blend    the objects, or the errors found
#                                         so far, `FILE:LINE: message`
#                                         in line order (`blend-objects`)
#   bend blend.bend resolve FILE.blend    each concrete object's copies
#                                         and what their names reach
#                                         (`blend-resolve`)
#   bend blend.bend emit FILE.blend [ROOT...]
#                                         the emitted module, all of it or
#                                         what the roots reach, by their
#                                         emitted names (`blend-emit`)
#
# blend/run.sh runs the same, built once (blend/build.sh).

def base.k(r: List<&2, U32> & List<&2, U32>) -> String:
  (a, b) = r
  text(List.reverse(&2, U32, a))

# a path's last part, as messages name the file
def basename(path: String) -> String:
  base.k(until(List.reverse(&2, U32, codes(path)), 47))

def usage() -> String:
  "usage: bend blend.bend read|objects|resolve FILE.blend, or emit FILE.blend [ROOT...]"

# 1 read, 2 objects, 3 resolve, 4 emit
def run(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, +bs: List<&2, U32>) -> Out:
  match cmd:
    case 1:
      Out{True{}, show(read(bs), List.length(&2, U32, bs))}
    case 0:
      Out{False{}, usage()}
    case _:
      objects(cmd, file, roots, read(bs))

# the output printed; errors to stderr, and the exit status 1
def main.out(o: Out) -> IO(Unit):
  match o:
    case Out{+ok, text}:
      match ok:
        case True{}:
          IO.print(text)
        case False{}:
          do IO<Unit>:
            IO.print_err(text)
            IO.exit(1)

def main.read(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, fr: File & Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  (f, r) = fr
  match r:
    case Done{bs}:
      do IO<Unit>:
        File.close(f)
        main.out(run(cmd, file, roots, bs))
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        main.out(Out{False{}, "blend: cannot read the file"})

def main.size(+cmd: U32, +file: String, +roots: List<&2, List<&2, U32>>, fs: File & Result<&1, &1, U32 & String, U32>) -> IO(Unit):
  (f, r) = fs
  match r:
    case Done{+n}:
      do IO<Unit>:
        fr : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, n)
        main.read(cmd, file, roots, fr)
    case Fail{e}:
      do IO<Unit>:
        File.close(f)
        main.out(Out{False{}, "blend: cannot size the file"})

def main.file(+cmd: U32, +path: String, +roots: List<&2, List<&2, U32>>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "r"))
    fs : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    main.size(cmd, basename(path), roots, fs)

def args.names(xs: List<String>) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{codes(x), args.names(t)}

def main.cmd(+cmd: U32, xs: List<String>) -> IO(Unit):
  match cmd:
    case 0:
      main.out(Out{False{}, usage()})
    case _:
      match xs:
        case Con{path, r}:
          main.file(cmd, path, args.names(r))
        case Nil{}:
          main.out(Out{False{}, usage()})

def cmd.of(+rd: Bool, +ob: Bool, +rs: Bool, +em: Bool) -> U32:
  match rd ob rs em:
    case True{} _ _ _:
      1
    case False{} True{} _ _:
      2
    case False{} False{} True{} _:
      3
    case False{} False{} False{} True{}:
      4
    case False{} False{} False{} False{}:
      0

def main.args(xs: List<String>) -> IO(Unit):
  match xs:
    case Con{p, r}:
      match r:
        case Con{+flag, r2}:
          main.cmd(cmd.of(String.eq(flag, "read"), String.eq(flag, "objects"), String.eq(flag, "resolve"), String.eq(flag, "emit")), r2)
        case Nil{}:
          main.out(Out{False{}, usage()})
    case Nil{}:
      main.out(Out{False{}, usage()})

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    main.args(xs)
